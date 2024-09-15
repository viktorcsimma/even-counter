#include "View/MainWindow.h"
#include "View/ui_MainWindow.h"

#include "View/HistoryItemWidget.h"
#include "View/PreciseOutputWindow.h"

#include <QKeyEvent>

MainWindow::MainWindow(MainViewModel& viewModel, QWidget *parent)
    : QMainWindow(parent)
    , ui(new Ui::MainWindow)
    , viewModel(viewModel)
{
    ui->setupUi(this);

#if defined(WIN32) || defined(__APPLE__)
    // Windows and OS X do not use the Button field of the colour palette;
    // so we have to paint the special buttons using stylesheets.
    // But setting the background colour is not too native-feeling here;
    // so let's just give a bold text.
    QString specialStyleSheet("font-weight: bold; color: unset");
    ui->enterButton->setStyleSheet(specialStyleSheet);
    ui->preciseOutputButton->setStyleSheet(specialStyleSheet);
#endif

    // control buttons
    connect(ui->enterButton, &QPushButton::clicked, this, &MainWindow::enterClicked);
    connect(ui->preciseOutputButton, &QPushButton::clicked, this, &MainWindow::preciseOutputButtonClicked);
    // this when settingsButton has been readded
    // connect(ui->settingsButton, &QPushButton::clicked, this, &MainWindow::settingsButtonClicked);

    // numpad buttons
    connect(ui->numButton0, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("0");});
    connect(ui->numButton1, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("1");});
    connect(ui->numButton2, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("2");});
    connect(ui->numButton3, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("3");});
    connect(ui->numButton4, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("4");});
    connect(ui->numButton5, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("5");});
    connect(ui->numButton6, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("6");});
    connect(ui->numButton7, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("7");});
    connect(ui->numButton8, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("8");});
    connect(ui->numButton9, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("9");});

    // operators
    connect(ui->addButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("+");});
    connect(ui->subtractButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("-");});
    connect(ui->multiplyButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("*");});
    connect(ui->divideButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("/");});
    connect(ui->powerButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("^");});

    // constants
    connect(ui->piButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("pi");});
    connect(ui->eButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("e");});

    // functions
    connect(ui->sqrtButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("sqrt(");});
    connect(ui->expButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("exp(");});
    connect(ui->sinButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("sin(");});
    connect(ui->cosButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("cos(");});

    // syntactic symbols
    connect(ui->decimalPointButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText(".");});
    connect(ui->leftBracketButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("(");});
    connect(ui->rightBracketButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText(")");});

    // history elements
    connect(ui->ansButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("Ans");});
    connect(ui->historyButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("history[");});
    connect(ui->rightSquareBracketButton, &QPushButton::clicked, ui->primaryLineEdit, [=](){ui->primaryLineEdit->addToText("]");});

    // connect keyboard Enter in the line edit to the corresponding slot
    connect(ui->primaryLineEdit, &QLineEdit::returnPressed, this, &MainWindow::enterClicked);

    // and select the line edit by default
    ui->primaryLineEdit->setFocus();
}

MainWindow::~MainWindow()
{
    delete ui;
    // but the view model does _not_ get destructed; that happens in the main function
}

void MainWindow::enterClicked()
{
    // Beware: they might be pressing enter again!
    // Let a double enter be a shortcut for opening the precise output window.
    if (ui->primaryLineEdit->containsResult()) {
        preciseOutputButtonClicked();
    } else {
        std::string command(ui->primaryLineEdit->text().toStdString());
        viewModel.enterCommand(command.c_str());
        ui->secondaryOutputLabel->setText(QString::fromStdString(viewModel.getSecondaryText()));
        if ("error" != viewModel.getSecondaryText().substr(0, 5)) {
            ui->primaryLineEdit->setResult(QString::fromStdString(viewModel.getPrimaryText()));

            // adding item to history list
            const int numberOfItemsBefore = numberOfHistoryItems();
            HistoryItemWidget* newWidget =  new HistoryItemWidget(
                numberOfItemsBefore + 1,
                QString::fromStdString(command),
                ui->primaryLineEdit->text() + " :: " + ui->secondaryOutputLabel->text(), ui->historyVerticalLayoutWidget
            );
            ui->historyVerticalLayoutWidget->layout()->addWidget(newWidget);
            connect(newWidget, &HistoryItemWidget::clicked,
                    ui->primaryLineEdit, [=](){
                ui->primaryLineEdit->addToText("history[" + QString::number(numberOfHistoryItems() - newWidget->getId()) + "]");
            });
        }
    }
}

void MainWindow::settingsButtonClicked()
{
    throw "not implemented";
}

void MainWindow::preciseOutputButtonClicked()
{
    PreciseOutputViewModel preciseOutputViewModel = viewModel.spawnPreciseOutputViewModel();
    PreciseOutputWindow preciseOutputWindow(preciseOutputViewModel, this);

    // this blocks;
    // that is why the reference remains valid
    preciseOutputWindow.exec();

    // and when it closes:
    ui->primaryLineEdit->setFocus();
}

int MainWindow::numberOfHistoryItems() const {
    return ui->historyVerticalLayoutWidget->layout()->count();
}
