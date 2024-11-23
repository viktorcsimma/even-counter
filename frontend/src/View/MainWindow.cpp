#include "View/MainWindow.h"
#include "View/ui_MainWindow.h"

#include <QErrorMessage>

MainWindow::MainWindow(QWidget *parent)
    : QMainWindow(parent)
    , ui(new Ui::MainWindow)
    , viewModel(new MainViewModel())
{
    ui->setupUi(this);

    ui->label->setText(QString::fromStdString(viewModel->getDisplayedText()));

    connect(ui->addButton, &QPushButton::clicked, this, &MainWindow::addButtonClicked);
    connect(ui->asyncButton, &QPushButton::clicked, this, &MainWindow::asyncButtonClicked);

    // We do this in order to ensure that the functions setting the UI run on the main thread.
    connect(this, &MainWindow::updateRequested, this, &MainWindow::updateUI);
    connect(this, &MainWindow::lastIterationFinished, this, &MainWindow::onLastIterationFinished);
}

MainWindow::~MainWindow()
{
    delete ui;
    delete viewModel;
}


void MainWindow::addButtonClicked()
{
    viewModel->incrementWith(ui->spinBox->value());
    ui->label->setText(QString::fromStdString(viewModel->getDisplayedText()));
    updateUI();
}

void MainWindow::asyncButtonClicked()
{
    if (viewModel->isEvaluating()) {
        viewModel->interrupt();
        ui->asyncButton->setText("Increase continuously");
    } else {
        ui->asyncButton->setText("Interrupt");

        // For now, the waiting period will be constant 5 seconds;
        // it's enough for demonstration.
        // And we do not need separate functions for separate cases either.
        viewModel->incrementManyTimesAsync(5, {std::function<void(int)>([this](int){emit updateRequested();})},
                                            {std::function<void(int)>([this](int){emit lastIterationFinished();})});
    }
}

void MainWindow::updateUI() {
    ui->label->setText(QString::fromStdString(viewModel->getDisplayedText()));
    if (viewModel->hasError()) {
        QErrorMessage errorMessage(this);
        errorMessage.showMessage("The backend has indicated a problem; is the value to add even?");
        errorMessage.exec();
    }
}

void MainWindow::onLastIterationFinished() {
    ui->asyncButton->setText("Increase continuously");
}
