#include "View/MainWindow.h"
#include "View/ui_MainWindow.h"

#include "ViewModel/OddParameterException.hpp"

#include <QMovie>

#include <stdio.h>

MainWindow::MainWindow(MainViewModel& viewModel, QWidget *parent)
    : QMainWindow(parent)
    , ui(new Ui::MainWindow)
    , viewModel(viewModel)
{
    ui->setupUi(this);

    ui->label->setText(QString::fromStdString(viewModel.getDisplayedText()));

    connect(ui->addButton, &QPushButton::clicked, this, &MainWindow::addButtonClicked);
    connect(ui->asyncButton, &QPushButton::clicked, this, &MainWindow::asyncButtonClicked);

    // We do this in order to ensure that onAsyncEnded runs in the main thread.
    connect(this, &MainWindow::asyncEnded, this, &MainWindow::onAsyncEnded);

    // If the value of the spin box is changed, we remove the error signs.
    connect(ui->spinBox, &QSpinBox::valueChanged, this, &MainWindow::unsetError);
}

MainWindow::~MainWindow()
{
    delete ui;
    // but the view model does _not_ get destructed; that happens in the main function
}

void MainWindow::setError() {
    QPalette pal = QPalette();
    pal.setColor(QPalette::Text, Qt::red);

    ui->spinBox->setAutoFillBackground(true);
    ui->spinBox->setPalette(pal);

    ui->spinBox->setToolTip("Tried to add an odd number to the counter.");
    ui->addButton->setToolTip("Tried to add an odd number to the counter.");
}

void MainWindow::unsetError() {
    ui->spinBox->setPalette(QPalette());
    ui->spinBox->setToolTip("");
    ui->addButton->setToolTip("");
}

void MainWindow::addButtonClicked()
{
    try {
        viewModel.incrementWith(ui->spinBox->value());
        ui->label->setText(QString::fromStdString(viewModel.getDisplayedText()));
    } catch (OddParameterException e) {
        setError();
    }
}

void MainWindow::asyncButtonClicked()
{
    if (viewModel.isEvaluating()) {
        ui->asyncButton->setEnabled(false);
        ui->addButton->setEnabled(false);
        viewModel.interruptEvaluation();
    } else {
        unsetError();
        ui->asyncButton->setText("Interrupt");

        // For now, the waiting period will be constant 5 seconds;
        // it's enough for demonstration.
        // And we do not need separate functions for separate cases either.
        viewModel.increaseForAsync(5, [this](){emit asyncEnded();}, [this](){emit asyncEnded();});
    }
}

void MainWindow::onAsyncEnded() {
    ui->label->setText(QString::fromStdString(viewModel.getDisplayedText()));
    ui->asyncButton->setEnabled(true);
    ui->addButton->setEnabled(true);
    ui->asyncButton->setText("Increase continuously");
}
